import { describe, it, expect, vi, beforeAll, afterEach } from 'vitest';

beforeAll(async () => {
  await import('../custom_components/foxess/scheduler_card.js');
});

afterEach(() => {
  document.body.innerHTML = '';
});

const DEVICE_SN = 'SN123456';
const SWITCH_ID = 'switch.foxess_mode_scheduler';

function makeHass(switchState, callService) {
  return {
    states: {
      [SWITCH_ID]: {
        state: switchState,
        attributes: { scheduler_groups: [], device_sn: DEVICE_SN },
      },
    },
    callService: callService ?? vi.fn().mockResolvedValue(undefined),
    connection: {
      sendMessagePromise: vi.fn().mockResolvedValue({ templates: [] }),
    },
  };
}

function mountCard(hass) {
  const Card = customElements.get('foxess-scheduler-card');
  const card = new Card();
  document.body.appendChild(card);
  card.hass = hass;
  return card;
}

describe('scheduler entity discovery', () => {
  it('shows a placeholder when no Mode Scheduler switch exists', () => {
    const card = mountCard({ states: {}, connection: { sendMessagePromise: vi.fn() } });
    expect(card.shadowRoot.textContent).toContain('No FoxESS scheduler entities found.');
  });

  it('ignores switches without scheduler_groups', () => {
    const hass = makeHass('on');
    hass.states['switch.other'] = { state: 'on', attributes: {} };
    const card = mountCard(hass);
    expect(card.shadowRoot.querySelector('.toggle-btn')).not.toBeNull();
  });
});

describe('toggle button rendering', () => {
  it('shows "enabled" with status-on class when the switch is on', () => {
    const card = mountCard(makeHass('on'));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    expect(btn.textContent.trim()).toBe('enabled');
    expect(btn.classList.contains('status-on')).toBe(true);
    expect(btn.classList.contains('status-off')).toBe(false);
  });

  it('shows "disabled" with status-off class when the switch is off', () => {
    const card = mountCard(makeHass('off'));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    expect(btn.textContent.trim()).toBe('disabled');
    expect(btn.classList.contains('status-off')).toBe(true);
    expect(btn.classList.contains('status-on')).toBe(false);
  });

  it('shows "unavailable" when the switch is unavailable', () => {
    const card = mountCard(makeHass('unavailable'));
    expect(card.shadowRoot.querySelector('.toggle-btn').textContent.trim()).toBe('unavailable');
  });
});

describe('toggle button click', () => {
  it('turns the switch off when the scheduler is currently enabled', () => {
    const call = vi.fn().mockResolvedValue(undefined);
    const card = mountCard(makeHass('on', call));
    card.shadowRoot.querySelector('.toggle-btn').click();
    expect(call).toHaveBeenCalledWith('switch', 'turn_off', { entity_id: SWITCH_ID });
  });

  it('turns the switch on when the scheduler is currently disabled', () => {
    const call = vi.fn().mockResolvedValue(undefined);
    const card = mountCard(makeHass('off', call));
    card.shadowRoot.querySelector('.toggle-btn').click();
    expect(call).toHaveBeenCalledWith('switch', 'turn_on', { entity_id: SWITCH_ID });
  });

  it('does nothing when the switch is unavailable', () => {
    const call = vi.fn();
    const card = mountCard(makeHass('unavailable', call));
    card.shadowRoot.querySelector('.toggle-btn').click();
    expect(call).not.toHaveBeenCalled();
  });

  it('disables the button while the request is in flight', () => {
    const card = mountCard(makeHass('on', vi.fn().mockReturnValue(new Promise(() => {}))));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    btn.click();
    expect(btn.disabled).toBe(true);
  });

  it('re-enables the button when the request fails', async () => {
    const call = vi.fn().mockRejectedValue(new Error('Network error'));
    const card = mountCard(makeHass('on', call));
    const btn = card.shadowRoot.querySelector('.toggle-btn');
    btn.click();
    await new Promise(resolve => setTimeout(resolve, 0));
    expect(btn.disabled).toBe(false);
  });
});
